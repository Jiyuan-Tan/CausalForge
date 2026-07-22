# F7 — substrate promotion recipe

Dispatch payload for the F7 promotion agent (see `SKILL.md` § "F7 — SUBSTRATE PROMOTION"). This is a
plain reference doc, not a skill — main hands the dispatched subagent this file path directly (`Read` it),
the same way `causalsmith-shared/reference.md` is a pointed-to store rather than an invoked skill. The
promotion agent is a single bounded task: no resume-lease, no `state.json`/node-process interaction — it
edits Lean/JSON files and runs `lake`/`npm` commands, then reports back and is done.

**Promotion SET** (given at dispatch): a list of `helper → target Causalean module` pairs, already
selected by main for REAL reuse — the agent does not re-litigate the selection, only executes it. A pair may
carry a **`generalize`** tag (target = a decoupled general statement): restate the lemma over a general
ambient, then re-import the run's version as a specialization. **Stop and report it back** — never
promote/gerrymander anyway — if a listed helper is actually high-coupling / a vestigial-import false
positive, or if a `generalize` pair has no faithful general form.

For EACH helper in the SET:

1. **Search Causalean AND Mathlib first** (`npm run search -- "<concept>" --scope module`; Mathlib via
   loogle / leansearch / `exact?`). If the concept already exists (e.g. a Krull-dimension or semialgebraic
   notion), **state the result in terms of it** — never mint a paper-named parallel primitive; a duplicate
   abstraction is the main long-term-maintenance cost. Reinventing an existing primitive is worse than none.
2. **Fit, don't dump.** The final target must be in the proper existing Causalean subject hierarchy.
   Search the current layout and place the result under the narrowest relevant domain (`Mathlib/`, `Stat/`, `SCM/`, `PO/`,
   `Estimation/`, etc.), creating a properly named topic module there only when no existing module fits.
   Match the target module's idiom: naming and notation (no run-jargon in shared
   names), generality, and file granularity (CLAUDE.md: one topic, normally ≤600 lines; split before ~900 when independent). Strip run-coupled types
   from the statement where the lemma is genuinely general; if it can't be stated without them, it wasn't
   low-coupling — stop and report (above).
3. **Move** statement + proof into the target module; rewire CausalSmith to re-import it (delete the local
   copy — never two definitions). **Causalean NEVER imports CausalSmith.**
4. **Docstring-canonical** (CLAUDE.md): first paragraph = self-contained NL translation; `/-! -/` module
   overview.
6. **Curate importance.** Add every MAIN result (identification/estimand-characterization theorem,
   paper-named decomposition, asymptotic linearity/normality/rate/optimality/efficiency result, sharp
   bound) to `headline_theorems` in `doc/library_review/<Area>.json` so the `/library` explorer shows its
   full NL card; leave supporting-tier lemmas (measurability/integrability, rewrites, bridges, intermediate
   inequalities) uncurated — don't over-list.
7. **New module/namespace.** If this lands a module with no existing sidecar coverage, also add a short
   one-line description — `namespace_intros["<Path>"]` for an inner namespace (dotted path below the area,
   e.g. `"Privacy"`, `"CATE.OSL"`) or `intro` for a brand-new top-level area — in
   `doc/library_review/<Area>.json`. Skip this when the module is already described.
8. **Regenerate derived views:** `lake exe library_index` → `embed:library` + `lint:embeddings` →
   `doc:gen`/`doc:check`.

**Mandatory self-check before reporting done — a report without this evidence is INVALID** (same
discipline as F's `f5-clean`: the agent's own claim never substitutes for the check main will
independently redo). After the moves, for the banked flagship theorem this run produced:

- **FULL** `lake build` (not a targeted module build — it can Replay a stale olean over a live error) →
  green.
- `#print axioms` on the flagship, via `lake env lean` (never `lean_verify`/LSP — stale-olean risk in
  either direction) → unchanged from the pre-promotion bank.
- Signature unchanged (no new binder), conjuncts intact.
- Grep the SOURCE for `sorry`/`admit`/`native_decide`/a stray `axiom` — lake exits 0 WITH sorries, so a
  green build alone is not evidence.
- **Fit:** you searched Mathlib + Causalean and either reused an existing primitive or can justify the new
  one; no run-jargon leaked into shared names.

**Report back, per helper:** promoted path, full build status, the `#print axioms` output. Main
independently re-verifies the regression gate itself before accepting — attach real evidence, not a
summary claim. If ANY check fails, do not "fix" it by weakening the banked flagship — **report the
failure and stop; main decides.**

**Record:** append the new Causalean paths to the bank README's `reusable_artifacts` field — main appends
the `command` decision-log entry after accepting the report.
