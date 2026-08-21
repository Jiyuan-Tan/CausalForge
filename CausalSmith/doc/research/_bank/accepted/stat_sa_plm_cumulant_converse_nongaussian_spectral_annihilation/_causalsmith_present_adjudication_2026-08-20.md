# PRESENT P1 adjudication — 2026-08-20 (re-plan after pipeline upgrades)

Supersedes the 2026-08-15 record for the P1 layer; the 2026-08-15 statement-audit
outcomes are unchanged and still stand.

## Why the layer was rebuilt

The 2026-08-15 P1 products predate the current presentation pipeline. Re-entering
with `--from P1` regenerated them. Two structural changes followed automatically:

- The frozen layer went from 105 blocks (46 graph envs plus 59 presentation-synthesized
  micro-definitions, including fourteen near-duplicate "clipped supplied code" entries)
  to the graph envs alone. Notation now resolves through table homes rather than
  synthesis.
- The outline moved to standard working-paper shape: sentence-case section names, a
  Related work section directly after the introduction, and the main root-n theorem
  promoted out of the certified-construction appendix into a main-results section.

## Notation adjudication

The first P1 pass halted: the notation reviewer returned the same eight findings on
two consecutive iterations. Triage:

REAL — three symbols were used in frozen statements with no anchored definition
anywhere in the layer:

- `b_n(X)`, the outcome contamination in `lem:observable-factorization`, which the
  rendered statement introduced only as "the outcome-contamination term entering the
  residual transform".
- `a_{1,n}, b_{1,n}, a_2, b_{2,n}` in `def:jms-eligibility`, which referred to them
  through a floating "condition (21)" pointer into the source paper.
- `Q_{P,1-\gamma}`, used by `def:minimax-risks`, `prop:jms-ace-alignment`,
  `thm:adaptive-rootn-minimax`, and `thm:local-to-gaussian-partial-benchmarks`, and
  defined by none of them.

A fourth, latent, defect was found while diagnosing these: `D_n` was homed on
`lem:l1-nuisance-zero-free`, an Appendix B lemma, but first used in
`lem:observable-factorization` in the main text — a definition-order failure waiting
for P3.

FALSE POSITIVE — two findings were checked against the rendered layer and rejected:

- `\Pi_{[-C_\theta,C_\theta]}` is defined in `def:sine-estimator`
  ("Here \Pi_{[-C_theta,C_theta]}(u)=min{max{u,-C_theta},C_theta}"), which precedes its
  only other use, `lem:gaussian-rademacher-l1-benchmark`.
- The `\mathcal P_{\mathrm{ACE},n}^{\mathrm{JMS}}` finding on
  `lem:non-gaussian-hard-submodel` was self-refuting ("use the already defined class
  symbol X instead of X"). `def:jms-ace-class` defines that symbol in its title and
  body, is placed earlier, and is correctly `\cref`-ed at the flagged use.

STALE — `\widehat\theta_{\mathrm{ad}}` and `\mathcal C_n(\delta_n)` were carried over
as notation-table rows with an empty use set; the regenerated table drops them.

## Bank graph edits

Backup: `graph.json.bak-2026-08-20`. Three anchored definition nodes were added, each
Lean-backed, together with eighteen `statement-uses` edges (from every consumer, and
from each new node to every definition its own symbols resolve to):

- `def:generalized-quantile` (P-15) — `generalizedQuantile`, `Basic.lean`. Promoted the
  existing extracted node `aux_generalizedQuantile` in place, so its three consumer
  edges carried over unchanged.
- `def:outcome-contamination` (P-16) — `outcomeContamination`, `Basic.lean`. Bundles
  `treatmentError` so `D_n` gets a main-text home alongside `b_n`.
- `def:jms-eligibility-quantities` (P-17) — `jmsA1`, `Helpers/JmsComparator.lean`.
  Bundles `jmsB1`, `jmsA2`, `jmsB2`.

`review.status` is recorded as `matched` with `passed_hash` set to the sha1 of the NL
statement, not to an F-stage review hash; each `review.note` says so. The mappings are
asserted by the operator and independently re-checked by the P1 statement-equivalence
audit against the named declarations.

Ordering was verified with the pipeline's own `loadGraph`/`renderedNodes`/`topoOrder`:
49 rendered envs, no statement-uses cycle, and the new definitions land early among the
definitions without displacing `def:minimax-risks` or `def:jms-eligibility`.

These edits add reader-facing definitions for objects the Lean already carries. They do
not strengthen, weaken, or restate any accepted mathematical claim.

## Second and third notation passes

Two further rounds of graph repair were needed before the layer became
self-contained. Each round re-rendered only the flagged environments; renders
were otherwise served from cache.

Round 2 — reader-order and missing setup:

- `def:model-parameters` (P-18, `Parameters`) and `def:plm-model` (P-19, `Model`)
  were added at the head of the setup section. Without them the section stated
  all sixteen assumptions before the class definitions that introduce
  `P`, `\eta`, `\xi`, and `r`, which the pipeline's own definition-order lint
  rejects and which no reader would accept either. Both are operator-frozen with
  field-by-field review notes.
- `def:model-parameters` also carries three standing conventions: `N(m,v)` for
  the Gaussian law, `\mathbb P_n` for the empirical average, and the Luxemburg
  sub-Gaussian spelling. The last one matters: the Lean has no norm at all —
  `EtaSubGaussian` and `XiSubGaussian` are the exponential-moment inequalities
  `\int \exp(\eta^2/\psi_\eta^2)\,dP \le 2` and
  `E[\exp(\xi^2/\psi_\xi^2)\mid X] \le 2` — so the convention paragraph is the
  bridge that makes the paper's `\lVert\cdot\rVert_{\psi_2}` notation mean
  exactly what the declarations assert.
- `def:outcome-contamination` was extended to display
  `B_n(z)=E_P[b_n(X)e^{zD_n(X)}]` and remapped from `outcomeContamination` to
  `contaminationTransform`, the declaration that actually realizes `B_n`.
- `def:sine-estimator`: the displayed definition of the clipping projection was
  moved from a trailing sentence to the opening sentence so it precedes its
  first use. Pure reordering.

Round 3 — formalization vocabulary in reader-facing displays:

- `prop:jms-ace-alignment` printed the Lean identifier `\mathrm{searchRadius}(p)`
  inside two displayed inequalities. It is the outer contour radius already named
  `R_1` by `def:contour-bank-handle`. Every occurrence was renamed to `R_1`, a
  naming clause was added, and the body was operator-frozen so the rename
  survives re-rendering.
- `thm:common-experiment-dichotomy` (locked) uses the parameterized fixed-code
  class `\mathcal P_{\mathrm{NG},n}(p;\bar g_n,\bar q_n)`, which no environment
  displayed. Rather than edit the locked theorem, `def:minimax-risks` was
  extended to display the parameterization for all three classes and all three
  risks. This moves the paper toward Lean rather than away from it: `minimaxRisks`
  takes `(p) (n) (gcode qcode)` explicitly and cuts each class with
  `barG p m n = clippedTreatmentCode p gcode n`, so the explicit argument list is
  what the declaration says.

## Statement audit: four mathematical corrections

The P1 statement equivalence audit halted twice. Two of the halts were genuine
disagreements between the frozen paper statement and the Lean, both corrected
toward the Lean; a third and fourth were found the same way.

1. `thm:exact-contour-identification` printed the bank index range as
   `{0,…,J}`. The Lean indexes bank radii by `Fin (JBase+1)` and defines
   `ContourBankData.J = JBase + 1` as the CARDINALITY of the bank, so the range
   is `{0,…,J_base}`. Off-by-one, corrected; `J` itself was also undefined
   anywhere in the layer and is now displayed in `def:contour-bank-handle`.
2. `def:adaptive-contour-estimator` claimed the evaluation-fold mesh is built
   from a derivative bound for the already normalized integrand
   `V_j(t) = rho_j e^{2 pi i t} (Ghat/Fhat) / N_j`. The Lean does the opposite:
   `momentLipschitzBound` carries no `1/N` factor and `evaluationFinish` applies
   `boundedContourNormalize` to the finished `CircleMesh.integralEnclosure`. The
   certified zero count divides the enclosure, not the integrand.
3. The same environment then still asserted
   `∫_0^1 V_j(t) dt = (N_j 2 pi i)^{-1} ∮ Ghat/Fhat dz`. With `V_j` unnormalized
   and `dz = 2 pi i rho_j e^{2 pi i t} dt`, the correct identity carries no
   `N_j`. The claim was split into the unnormalized identity plus the
   post-quadrature normalization, and the width guarantee was moved onto the
   normalized rectangle.
4. `def:minimax-risks`: the operator's own fixed-code edit enumerated three
   restricted classes including the published ACE class, which `minimaxRisks`
   does not cut. Restated as a notational convention on an arbitrary class.

## Bundled-packaging adjudications

Four environments map to one declaration each but display several. Each was
checked declaration by declaration and its `equivalence_cache.json` entry
reseeded to `faithful` under its stamped key (backup:
`equivalence_cache.json.bak-2026-08-20`), with the mapping written into the
entry's `detail` so a future reseed is a lookup rather than a re-derivation:

| environment | mapped decl | other decls the body displays |
| --- | --- | --- |
| `def:contour-functional` | `contourFunctional` | `learnedResidual`, `residualMGF`, `outcomeResidualTransform`, `nuisanceMGF`, `contourCount` (Helpers/Transforms.lean) |
| `def:plm-model` | `Model` | `Obs`, `eta`, `xi`, `barG`, `barQ`, `covariateLaw` (Basic.lean) |
| `def:model-parameters` | `Parameters` | `empiricalMean`, `fold0`, `fold1`, `gaussianReal`, `EtaSubGaussian`, `XiSubGaussian` |
| `def:jms-eligibility-quantities` | `jmsA1` | `jmsB1`, `jmsA2`, `jmsB2` (Helpers/JmsComparator.lean) |

The auditor is capable of accepting such a bundle — its own verdict for
`def:jms-ace-class` reads "The paper bundles the parameter, model, and
class-field declarations exactly … all match the listed Lean pieces" — but it is
not told which declarations a bundle claims, so it flags them inconsistently.

## Outline checkpoint

Reviewed and approved by the operator. Checked: sentence-case section names; a
Related work section directly after the introduction, carrying the quantitative
comparison against the competitor's own order-\(r\) ACE bound; setup ordered
parameters, then model, then assumptions, then classes; the headline theorems
in a main-results section rather than in an appendix; the verification-scope
appendix reduced to a scope note with no result of its own; every notation row
homed in an environment that precedes its first use, verified with the
pipeline's own `lintDefinitionOrder` (0 problems over the outline-ordered
layer); notation review `ok: true` with no advisories; all 51 environments
faithful to Lean.

## P2 status at the time of writing

P1 is closed. P2 (section drafting, proof rendering, proof audit) is running
detached; its PID is recorded in `_orch_logs/saplm_p2b.pid` (node PID in
`saplm_p2b.nodepid`, log `saplm_p2b.log`). All twelve sections and all sixteen
proofs are drafted and cached; the proof audit is in its refinement loop.

An earlier P2 attempt was killed when the harness reaped its background wrapper.
Nothing was lost — sections and proofs are file-cached and the audit cache is
content-keyed — but two lessons are worth keeping. First, launch any stage that
can outlive the wrapper detached (`setsid nohup`) from the start. Second, do not
test liveness with a `pgrep -f` pattern that your own monitoring commands also
contain: it matches the monitors and reports the run alive after it has died.
Check for the actual interpreter process instead.

## P2 draft checkpoint — APPROVED (operator, 2026-08-20)

**Outcome: all 20 proofs faithful to Lean.** Zero incomplete, zero unfaithful.

### The promotion rounds worked, and were not a runaway lemma pile
Two promotion rounds fired across the P2 attempts, and each one unblocked its target
rather than re-attacking a proof it had already failed:

| round | added | serves | result |
|---|---|---|---|
| 1 | `lem:gaussian-exponential-square-quarter-scale`, `lem:clipped-ratio-risk-decomposition` | `lem:non-gaussian-hard-submodel`, `lem:gaussian-rademacher-l1-benchmark` | both targets → faithful |
| 2 | `lem:luxemburg-mgf-envelope`, `lem:population-numerator-envelope` | `lem:zero-localization`, `thm:adaptive-rootn-minimax` | both targets → faithful |

The pause condition (a second firing on the *same* proofs, which would indicate the claim
rather than the scaffolding was wrong) never triggered. All four promoted nodes point at
**pre-existing, already-proved** Lean helpers — `Helpers/LuxemburgMGF.lean` (2026-08-16) and
`Helpers/PopulationNumeratorBound.lean` (2026-08-13) among them — with no sorries and proper
imports. The promotion round surfaces proved helpers into the paper; it does not invent
scaffolding to cover a bad claim. Graph went 265→267 nodes.

### Checked at this checkpoint
- 20/20 proof-audit verdicts `faithful`; `hard_gate_failures` empty.
- Every proof file's `\begin{proof}[Proof of \cref{obj:...}]` references its **own** object
  (no title/attribution slips from batch rendering).
- **Authorship standard respected.** No Lean declaration names, file paths, or proof-engineering
  structure in the visible main text; the sole mention of Lean is one pointer sentence in the
  introduction directing the reader to the crosswalk appendix. Per-step `% lean: <decl>` provenance
  is carried in LaTeX *comments*, so it is invisible in the rendered paper while remaining
  machine-checkable.
- Spot-audited `lem:population-numerator-envelope` line by line: the AM-GM step
  `8R|η| ≤ η²/ψ_η² + 16R²ψ_η²`, the Luxemburg fourth-moment bound `E|η|⁴ ≤ 4ψ_η⁴`, the
  conservative `(x+y+z)⁴ ≤ 64(x⁴+y⁴+z⁴)`, and `E[E] ≤ ‖E‖_{L²}` under a probability law
  are each correct.
- `front_matter.tex`: abstract + introduction with a roadmap paragraph. Contributions are
  stated in prose with `\cref` pointers rather than as a numbered list — accepted as natural
  working-paper style; a numbered list would duplicate the walkthrough.
- No `sorry`/`admit` anywhere in the bundle prose.

### Operator adjudications made during P2 (all manual, no pipeline changes)
1. **Three over-declared `statement-uses` edges dropped** — `lem:clipped-ratio-risk-decomposition`
   → `def:plm-model`, `lem:luxemburg-mgf-envelope` → `def:plm-model`. Both statements are generic
   over an arbitrary probability space (the Lean decls quantify over arbitrary `(X, μ)`) and resolve
   through nothing in the PLM model. One **real** dependency was cited instead of dropped:
   `lem:gaussian-exponential-square-quarter-scale` genuinely uses the `N(m,v)` convention from
   `def:model-parameters`, so it now cites it and its body is frozen.
2. **Stale notation rows re-pruned.** A promotion changes the env set, which invalidates the outline,
   which triggers a full codex outline regeneration — and that regeneration discards operator
   notation curation. Four stale rows returned (`θ̂_ad`, `ε₀`, `ρ_j=R_0+1/4+j2^{-m_⋆}`,
   `η_a=√(1-a²)G_∘+aS`); each was verified to have **zero** occurrences in `formal_layer.tex`
   before removal, so the notation-reviewer's "remove if unused" branch was the correct one and
   no frozen body needed editing. The `W` re-home to `def:model-parameters` was also reverted by
   the regeneration and reapplied (definition-order lint: 1 problem → 0).

### Reported for backlog (no fix authored, per the standing simplicity directive)
- Outline regeneration on env-set change silently discards operator notation curation. Bitten twice.
- The promotion round attaches boilerplate `statement-uses` edges to `def:model-parameters` and
  `def:plm-model` regardless of whether the promoted lemma uses them. Bitten three times. Not
  proposing a fix: the correct edge set is a per-lemma mathematical judgment.
- P2 emits no log output until a batch boundary, so an empty log during P2 is not evidence of a hang.
  Verify liveness by the interpreter PID plus accumulated CPU and live codex children.

## P4 emit — docstring backfill campaign (operator, 2026-08-20)

**P3 PASSED** (paper.pdf built, no gate failures). **P4 emit HARD-FAILED** on docstring coverage:
340 declarations in the run's Lean modules carried no docstring.

### Root cause — a structural gap, not this run's fault
Commit `d8d612e3` (2026-08-15 23:28) moved the docstring-coverage pass **from presentation P4
to research F5**. P4 previously *authored* docstrings mid-emit; it now only *verifies*. This entry
was banked before that move (no `docstring_coverage.json` exists anywhere), so its docstrings were
never authored — and F5 does not run on an already-banked entry. There is **no backfill entry
point** in `tools/bin/`. Every pre-2026-08-15 banked entry will hit this.

Second, independent constraint discovered here: **codex cannot run under operator authorization on
this cluster.** `codex exec --sandbox workspace-write` aborts at sandbox setup with
`bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted` (no system bubblewrap; the bundled
one cannot create a loopback in this Slurm namespace). The pipeline's own codex works only because
it passes `--sandbox danger-full-access`, which is outside the CLAUDE.md tooling grant. Any future
backfill command must therefore be callable **without** codex.

### What was done
Executor swapped to Claude subagents (no sandbox required); the pass otherwise mirrors F5 exactly —
F5's own prompt `src/formalization/prompts/F5/stage5_docstrings.txt` used **verbatim** with
`{{package_root}}` / `{{decl_list}}` substituted as `declListFor` does, model config read from
`MODEL_PLAN.stage5`. All 31 target files snapshotted byte-for-byte first (never `git checkout` —
that would destroy unrelated uncommitted work in this shared tree).

**325 of 325 authorable declarations documented across 31 files.** Every file verified with a
three-way checker (`scratchpad/docstrings/verify_docstring_only.py`): every hunk a pure insertion,
every inserted region reducing to empty after stripping `/-- -/` blocks, and deleting the inserted
lines reproducing the snapshot **byte-for-byte**. Totals: 325 insertion regions, ~1,430 lines added,
**0 deletions, 0 modifications**. Nothing required rollback. Full build of the run root module:
**exit 0, 0 errors**.

### Substantive catches (not mere formatting)
1. **Faithfulness error corrected.** `generalizedQuantile` evaluates `Causalean.Stat.quantile` at
   level `1-γ`, which for `γ ∈ (1/2,1)` is *below* one half. `quantile` is the **lower** generalized
   inverse, so an initial draft describing an upper-tail "error at most Q with probability ≥ γ"
   guarantee was **backwards**. Corrected to: the error *exceeds* that value with probability at
   least γ, so bounding it below is the high-probability form of the paper's converse.
2. **Restraint on unproved properties.** In `CertifiedTranscendental` the raw Taylor/atan enclosures
   are *definitions only* — nesting and intersection-soundness are proved, but that the raw intervals
   bracket the true transcendental values is **not** (it lives in the `…Contract` predicates). The
   docstrings say what each construction computes rather than asserting an unproved enclosure.
3. **Placement precedent verified, not assumed.** Docstrings sit *above* `-- @node:` markers;
   confirmed empirically that `minimaxRisks` has `doc: True` in the index with exactly that shape,
   so Lean attaches through an intervening line comment and `paper_index` extracts it.
4. **Operator error caught and fixed.** My exclusion heuristic wrongly filtered `npow`,
   `BoundedComplexMap.add`, `BoundedComplexMap.sub` as structure fields; all three are real
   hand-written `def`s. Authored in the file's house style rather than escalated as a gate bug.

### HALTED — gate defect escalated to the coordinator
P4 now reports **exactly 12**, down from 340. All are `line=0`, `kind=theorem`, `<name>.eq_def` —
Lean's auto-generated equation lemmas, emitted on demand when a definition is rewritten with. They
have no source position and **cannot carry a docstring**. Verified: **all 12 parent definitions are
indexed and documented**, so no authorable documentation is missing.

The defect is a missing exclusion in `LibraryIndexCore.lean`:
- `auxSuffixes` (L39-42) lists 18 compiler-generated suffixes; `eq_def` appears **nowhere** in the
  file (grep count 0).
- `shouldSkipDecl` (L94-98) already carries a bespoke exclusion for the sibling class with a
  rationale that applies verbatim: *"`@[congr]` synthesizes `<decl>.congr_simp` theorem constants.
  They have no authored declaration range or source; the declaration they support is indexed."*

Latent, not run-specific: `.eq_def` constants are generated only on demand, which is why
`d8d612e3`'s audit — which explicitly confirmed `congr_simp` constants absent — passed while
missing the neighbouring class.

**Not fixed here** (tools territory, coordinator's call): the two candidate sites differ in reach
(`isAuxiliary` vs `shouldSkipDecl`) and choosing wrong could silently drop real declarations from
the index — a worse failure than the current one.

State on halt: P1/P2/P3 verdict caches valid and untouched, 20/20 proofs faithful, full build green.
`--from P4` should walk through to P5 once the exclusion lands.

## P5 round — operator revision cycle (2026-08-20)

P5 halted after its two automatic passes: **major_revision, 6.2/10**.

### Defect 1 (objective): render-introduced word corruption inside FROZEN statements
Three places in the paper's formal statements had a word degenerate to a bare `u`:
the two headline bullets read `(Non-Gaussian fixed-code u.)` / `(ACE fixed-code u.)`, and the
Gaussian–Rademacher lemma read `Its mean squared u obeys`.

**PROVENANCE — CORRECTED 2026-08-20 (my first attribution was WRONG).** I originally concluded
from the frozen-body deltas (HEAD and the session-start backup carry **no** `frozen_body` on these
nodes, `statement` 3705 / 1755 chars and clean; the current graph has `frozen_body` at 3967 / 2752
chars containing the corruption) that "the Lean-aware render produced it and P3 froze it into the
bank". That inference does not follow: the deltas show only that a freeze happened during the
session, **not** that the render generated the text. I conflated "a `frozen_body` appeared" with
"the renderer authored its content".

The forensic conclusion is that **no pipeline code was involved**. The corruption entered through an
**operator hand-edit of `graph.json`** in the 09:34–09:39 window on 2026-08-20 — the de-Leanifying
freeze wave recorded above as "Round 2/3 operator-frozen". A per-env `risk` → `u` rename (mapping the
Lean binder `risk` in `thm:local-to-gaussian-partial-benchmarks` onto the symbol `u`) was applied as a
**plain-text replacement** and clobbered the English word "risk" in the prose of sibling envs rewritten
in the same wave. Supporting evidence: no model *output* anywhere in the 589k-line log contains the
corrupted strings before P5's echoes; the whole de-Leanified rewrite wave appears in zero outputs;
`p1_cache` renders are clean; deterministic transforms replay byte-identical on the clean bodies; and
snapshot diffs bracket the freeze to exactly that window. It was never a notation substitution — there
is no notation row for `u`.

**Restoration precision.** All three sites were the same replacement, and the clean text at the lemma
read "mean squared **risk**", where this repair restored "mean squared **error**". Semantically
identical (the Lean quantity is `mseRisk`, i.e. `E_P[(θ̂−θ₀)²]`), and "mean squared error" is the
standard econometrics phrasing for that quantity, so the wording was kept rather than re-edited —
another edit would move the content key again and re-open the audit for no semantic gain. Recorded
here so the record is exact.

**Do not restore from `graph.json.bak-2026-08-20-preP5fix`** — that snapshot still contains the
corruption (6 occurrences). It is retained only as forensic evidence. The live graph is clean (0).

**Lesson, now enforced in the pipeline.** The guard adopted later in this run for the 2π→64 edit —
asserting occurrence counts before and after every textual replacement — is precisely the discipline
that prevents this class, and it proved itself by throwing on a false count during that very edit. A
mangled-word lint now runs in `lintClarity` at every P1 review and in P4's paper scan.

Both referee rounds flagged it and **neither automatic pass could repair it**, because those passes
correctly refuse to edit frozen statements. Only an operator can.

Repaired from the Lean rather than from taste: `adaptive_rootn_minimax`'s docstring reads "matched
minimax MSE", the benchmark bounds `mseRisk`, and the layer already says "fixed-code JMS ACE minimax
risk" elsewhere → `risk` / `risk` / `error`. Wording only. A sweep of all 267 nodes for siblings of
this corruption class returned only false positives (`i.i.d.`, `obj:ass:g-range`, possessives), so
these three were the complete set.

**Gate observation (reported, not fixed):** the P1 statement audit ran after this text was frozen,
on several cycles, and reported "all frozen envs faithful" every time. Defensible — the audit checks
*mathematical* faithfulness and a mangled bullet label changes no mathematics — but the consequence
is that prose corruption inside a frozen statement is invisible to every gate except the P5 referee.

### Defect 2 (false positive): the `% lean:` complaint
The `[major·structure]` finding claims proof bodies "include Lean trace comments such as
`% lean: ...`". There are 147, **all unescaped LaTeX comments** (zero escaped `\%`), and **zero**
reach the rendered output (checked `paper_body.html`). The referee read `paper.tex` source, not the
paper. Not acted on. The remainder of that finding (implementation detail in the main text) may stand.

### Re-application of the bundled-packaging adjudication
The docstring backfill inserted docstrings into `Basic.lean` and `Helpers/Transforms.lean`, which
moved the **content-keyed** equivalence-audit keys and silently reverted three previously adjudicated
verdicts to `drift`: `def:model-parameters`, `def:plm-model`, `def:contour-functional`.

Verified before re-applying: all three frozen bodies are **byte-identical** to the adjudicated text
(sha `72f51a21f147`, `75e9daa7425c`, `ab5bca316313`; lengths 1219 / 1047 / 595), the auditor's
complaint is the *same* bundled-packaging class, and the fourth bundled entry
(`def:jms-eligibility-quantities`) was re-audited over the same docstring movement and returned
**faithful on its own** — so the auditor is not uniformly hostile to bundling.

Reseeded `drift → faithful` under the documented recipe with stored keys untouched, each detail
prefixed to record it as a **RE-APPLICATION** of the 2026-08-20 declaration-by-declaration
verification re-triggered by docstring-only key movement — *not* a fresh blessing.

**Interaction worth recording:** a docstring-only Lean edit invalidates equivalence-audit cache keys
and silently reverts operator adjudications. That is the mirror image of the observation above —
the audit key is sensitive to documentation text that carries no mathematics, yet tolerates prose
corruption inside the statement it is auditing.

### Scope: four findings NOT actioned (pipeline routed them out of scope)
A conditional-on-training corollary for random first stages; renaming the headline theorem away from
"Adaptive" (a frozen-statement title — equivalence-adjudication territory); additional foundational
citations; a simulation study. These are user-level scope calls.

### Sequencing note (why the cycle was split at P2)
`sectionCacheKey` (`p2_draft.ts:256`) hashes the **frozen env bodies each section places**, so
amending two frozen bodies invalidates exactly `04_main_fixed_separation_result` and
`06_explicit_mixture_reductions`. Those two *must* re-draft to carry the corrected wording into their
embedded env copies, which would silently discard any hand edits placed in them. Splitting the cycle
at `--stop-after P2` (redraft first, hand-edit after, then `--from P2 --reassemble`) removes that
discard path entirely rather than mitigating it, at identical P5 cost — reassemble **throws** on a
missing authored source instead of re-drafting (`p2_draft.ts:265, 407, 557`).
