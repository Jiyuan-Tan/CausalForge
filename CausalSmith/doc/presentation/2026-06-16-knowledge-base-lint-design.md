# Knowledge-Base Lint — Design Note

**Date:** 2026-06-16
**Status:** Draft for review (no code yet)
**Author:** drafted with Claude Code, pending human sign-off

## 1. Motivation

The repo runs ~70–80% of the "LLM wiki" pattern (Karpathy, gist `442a6bf…`)
already: `CLAUDE.md` is the schema layer, the library explorer is an
LLM-owned browsable knowledge product, the ideasmith study graph is the
concept graph, and the thmsmith/ideasmith/papersmith pipelines are the
ingest verbs. The one verb that is only **partially** built is *lint*.

There is a correctness asymmetry between two layers:

- **Formal layer — self-healing.** Each headline theorem's review stamp in
  `doc/library_review/<Area>.json` is pinned to `statementHash()` (a
  whitespace-insensitive SHA256 of the formal statement). Change the Lean
  statement → hash changes → the `/library` badge auto-flips to *stale*.
  `check_library_index.ts` additionally hard-fails CI on modules unreachable
  from the `Causalean.lean` root (the PolyTail incident, 2026-06-11).

- **Prose-about-Lean layer — frozen at write time.** The bank crosswalks
  (`<qid>_crosswalk_full.json`), the two `API.md` files, and the study-graph
  node references are written once and never re-validated against live Lean.
  A crosswalk asserts `obj_id T-1 ≡ Basic.lean:Uof, verdict: equivalent`;
  rename `Uof`, move it, or change its statement, and that assertion silently
  becomes false. Nothing detects it.

That asymmetry is where the knowledge base can rot silently — confident-looking
documentation drifting away from the code it describes. This is the failure
mode that kills human-maintained wikis; the project's whole premise (rigor,
type-checked correctness) makes it the right place to fix.

## 2. Goal / Non-goals

**Goal.** Port the formal layer's drift-detection discipline (statement-hash
staleness + reachability) onto the prose-about-Lean layer, so that **every
natural-language claim in the repo stays provably tied to a live formal
object**.

**Non-goals.**
- The lint **never adjudicates correctness of the Lean** — the type checker
  does that. The lint only checks that prose *points at* and *still matches*
  live formal objects.
- No rewrite of the formal core, no LLM-prose layer in front of verified
  content. Verification stays where it belongs.
- The Obsidian/navigability piece (§5) is optional convenience, explicitly
  secondary to the lint.

## 3. Background — what already exists (reuse, don't rebuild)

| Mechanism | Where | Covers |
|---|---|---|
| NL first-paragraph docstring required on tier-1 decls | `check_library_index.ts`, `nl_docstring.txt` | formal layer |
| Statement-hash review staleness | `site/src/lib/library.ts` `statementHash()`, `doc/library_review/<Area>.json` | formal layer |
| Orphan module CI fail | `check_library_index.ts` (walk `Causalean/` vs index `modules`) | formal layer |
| `usesSorry` / non-standard axiom surfacing | `LibraryIndexCore.lean` | formal layer |
| Per-result tex↔Lean map with verdicts | `<qid>_crosswalk_full.json` (`obj_id`, `lean:{file,decl,line}`, `verdict`, per-`clause` verdicts) | **frozen, unlinted** |
| Idea-map edges | `study/index.json` `forward` index | JSON-only, siloed |

The live formal index (`doc/library_index.json`, 4,438 decls with
name/module/file/line/statement/axioms) is the source of truth the lint
resolves prose references against.

## 4. Design — the lint checks

Ordered by value; "mechanical" = pure index lookup, no LLM; "LLM" = scoped
re-adjudication.

### C1. Crosswalk reference integrity (mechanical, highest value) — SHIPPED 2026-06-16
For every `*_crosswalk_full.json` in `_bank/`, resolve each `lean.{file,decl}`
against the entry's **live Lean source** (`state.json.lean_subdir`), NOT against
`library_index.json` — correction from the original draft: crosswalk anchors are
bare (`{file:"Basic.lean", decl:"…"}`) and point at CausalSmith theorem-output
files, which `library_index.json` (Causalean only) does not contain. Flag:
- decl no longer exists (renamed/removed) → **missing-decl** (broken anchor),
- decl moved to a different file basename → **moved-file**,
- recorded `line` drifted beyond tolerance → **line-drift** (informational).

This is the bank's analogue of the orphan check. Zero LLM.

Implementation:
- pure core + live-source index: `tools/src/formalization/bank_crosswalk_lint.ts`
  (reuses `parseAllDecls` from `crosswalk.ts`, now exported),
- CLI: `tools/bin/check_bank_crosswalks.ts` (`npm run lint:crosswalks`;
  `--json`, `--verbose`, `--strict` → exit 1 on any missing-decl/moved-file/
  unresolvable-lean-dir),
- tests: `tools/test/bank_crosswalk_lint.test.ts` (6 cases).

First live run (the 2 accepted entries, the only ones with crosswalks today):
**0 missing-decl, 0 moved-file, 24 line-drift** — structurally healthy, but every
anchor's line had drifted (e.g. T-2: 7770 → 5922), empirically confirming the §7
decision below. CI-warn (not hard-fail) initially; `--strict` is wired for when
it is promoted.

### C2. Crosswalk verdict freshness (LLM, scoped)
For each crosswalk obj whose referenced decl's `statementHash` changed since
the crosswalk's `banked_on`, mark its `verdict: equivalent` as **stale**
(mirrors the library-review badge). Only stale objs are re-adjudicated, and
results are content-keyed/cached (same discipline as papersmith P3 — never
re-run without material change).

### C3. API.md ↔ source file paths (mechanical) — SHIPPED 2026-06-16
For both `API.md` files, take the FIRST backtick path in each `## N. \`path\``
section header and check it exists on disk. SCOPE NARROWED from the draft: only
the section's canonical FILE PATH is checked, not decl names mentioned in prose
(resolving prose identifiers is noisy — false positives erode lint trust — and
belongs to the LLM C2 pass). Brace groups (`SCM/Do/{A, B}.lean`) are expanded;
glob tokens (`dir/*.lean`) are checked at their parent directory; tokens resolve
under the file's source root OR the workspace root (a few headers slip to
workspace-relative). Impl `tools/src/formalization/api_md_lint.ts`, tests
`tools/test/api_md_lint.test.ts` (8 cases).

First live run: **1 genuine rot, 0 false positives** (after glob/rooting
refinements). `doc/API.md` §9i documents `PO/ProxyBridge.lean`. Investigation:
the file was not merely moved — its lemmas (`matrix_sum_eq_cofactor_sum`,
`bridge_target_eq_pi_h`) now live ONLY in `archive/boundsmith(Archived)/`, and
the live proxy framework is a different restructured module set
(`Causalean.PO.ID.Partial.Proxy.*`). So §9i documents archived/removed material.
OUTSTANDING — needs a doc-authoring decision (remove §9i vs repoint to the live
`PO/ID/Partial/Proxy/` framework); not auto-edited (I did not author it, and the
two options diverge in content).

### C4. Study-graph ↔ bank consistency (mechanical) — SHIPPED 2026-06-16
Every `study/nodes/banked_theorem/*.json` carries a `qid`/`spec`: confirm a real
`_bank/<qid>_<spec>/` entry exists in some tier (dangling-node otherwise).
Conversely, every `accepted/` entry should have such a node (missing-node
otherwise) — the standing version of the ideasmith S5 reconciliation. Impl
`tools/src/study/study_bank_lint.ts`, tests `tools/test/study_bank_lint.test.ts`
(4 cases).

First live run flagged 4, of which 2 were a lint bug and 2 were genuine:
- **2 false positives → C4 corrected.** `manski_nonparametric_bounds_t2/t3_v1`
  looked dangling, but manski is banked in a SECOND bank root,
  `_literature_bank/accepted/` (study-mode bank, distinct from the research
  `_bank/`). C4 now scans BOTH roots (entry dir = any dir holding a README.md
  whose name is not a tier bucket; `accepted` inferred from the path). Lesson:
  the original draft assumed a single bank root — a false positive is worse than
  a miss, so the corpus boundary must be exhaustive.
- **2 genuine → fixed.** Both accepted flagship results
  (`stat_ate_overlap_decay_v1` / `stat_policy_regret_margin_overlap_v1`) had no
  `banked_theorem` node. Minted via the purpose-built `reconcile_bank.ts`
  (2 written, 7 existing unchanged). C4 is now clean.

CLI for C3+C4: `tools/bin/check_kb_consistency.ts` (`npm run lint:consistency`;
`--json`, `--strict` → exit 1 on any finding — all C3/C4 findings are actionable,
unlike C1's line-drift). `npm run lint:kb` runs C1+C3+C4.

### C5. NL hygiene checker (LLM, nice-to-have)
First-paragraph docstrings / API descriptions must contain no Lean-syntax
leakage (field projections like `B.sigma`, `∀`/`fun`/`Prop`, `inst` names) per
the `nl_docstring.txt` convention. `library_nl_sweep.ts` *drafts* these; there
is no standing *checker*.

**Invariant across all checks:** the LLM is used only for the bookkeeping
(does this prose still match this live statement?), never to certify the math.

## 5. Optional — Obsidian navigability (secondary)
A single generator emits an Obsidian-browsable vault from edges that *already
exist*: bank-README frontmatter qids + `study/index.json` `forward` index →
`.md` files with `[[wikilinks]]` and tags (`#status/accepted`,
`#tier/subfield`, `#novelty/field`). Pure transform of existing data — no new
knowledge work. Deferred behind the lint; convenience, not correctness.

## 6. Rollout

1. ~~**C1 first** — crosswalk reference integrity.~~ **DONE 2026-06-16.**
2. ~~**C3 + C4** — mechanical API.md / study-graph consistency.~~ **DONE
   2026-06-16** (`check_kb_consistency.ts`). Report-only; `--strict` wired.
   **CI:** `.github/workflows/kb-lint.yml` runs `npm run lint:kb:strict` on every
   push/PR as a WARN step (`continue-on-error`) — node-only, no Lean build.
   Findings surface non-blocking. Drop `continue-on-error` to promote to a gate.
3. **C2** — verdict freshness (LLM, cached). Promote C1+C3+C4 to CI hard-fail
   once stable. ← NEXT
4. **C5 / §5** — NL hygiene checker and Obsidian generator, opportunistic.

**Findings triage (2026-06-16 first runs).** C1: 0 broken (24 line-drift, info).
C3: 1 outstanding (§9i ProxyBridge — archived; needs doc decision). C4: 2 false
positives (manski — fixed by adding `_literature_bank`) + 2 genuine (stat nodes —
minted via `reconcile_bank.ts`). Net live state: **C1 clean, C4 clean, C3 has the
one ProxyBridge item pending a human call.**

Likely home: extend `CausalSmith/tools/bin/check_library_index.ts` or a
sibling `check_bank_crosswalks.ts`, reusing its index loader.

## 7. Open questions
- ~~Line-drift tolerance for C1, or drop line-matching entirely and key on
  `(file, decl)` only?~~ **RESOLVED (2026-06-16):** integrity keys on
  `(file, decl)`; line-drift is reported but never fails and is collapsed to a
  count in the default report. The first live run showed all 24 anchors drifting
  lines while 0 broke structurally — lines are noise, `(file, decl)` is stable.
- Should C2 staleness block papersmith re-emit, or only warn?
- Where do lint findings surface — a generated report md, CI annotations, or a
  `/library`-style status page?
- Is the study-graph reconciliation (C4) better left inside the ideasmith S5
  stage rather than duplicated in a standing lint?
