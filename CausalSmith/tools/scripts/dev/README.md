# scripts/dev — formalization debugging tools

Reusable, parameterized dev utilities for inspecting / testing the CausalSmith research
formalization gates without running the whole pipeline. Run from `tools/` on node 20
(`source ~/.nvm/nvm.sh && nvm use 20.20.2`).

## `hidden_defs.ts` — inspect the F2.5 hidden-def surface (no LLM)

Runs the deterministic `findHiddenStatementDefs` BFS and prints every build-inline
`def`/`structure`/ℝ-quantity reached from a theorem STATEMENT that becomes an `AUX-`
crosswalk row (what F2.5 check K and F4 audit). Pure TypeScript — no codex, instant.

```
npx tsx scripts/dev/hidden_defs.ts <qid> <spec>        # resolve leanDir from state
npx tsx scripts/dev/hidden_defs.ts --lean-dir <path>   # any Lean dir (abs or repo-relative)
```

Each row prints its `flavor` (`const-exist` | `structure` | `predicate` | `quantity`),
file:line, and the T-blocks that reach it.

## `f25_review_probe.ts` — run the F2.5 reviewer ALONE, no rewind

Calls `reviewWithCodex` directly (the reviewer half of F2.5), bypassing
`runReviewBoundary`, so the F2 producer never runs, nothing loops, and the Lean
scaffold is never edited. Faithful to the live gate (same skeleton + AUX rows +
`crosswalkReviewInstruction`). Prints the raw `ReviewResult` JSON. Use it to test a
prompt/detector change against a real scaffold.

```
npx tsx scripts/dev/f25_review_probe.ts <qid> <spec> [--tex <path>] [--keep]
```

- For a **banked** entry the research dir (which `artifactPaths` reads) has been
  cleaned, so the probe reconstitutes `<qid>_<spec>.{tex,md}` + `_state.json` from the
  bank, then deletes exactly what it created. `--keep` leaves them; `--tex <path>`
  overrides the note source (default: the bank's `*_LOCKED_d05accept_field.tex` /
  `*_d0r_best.tex` / `*field*.tex`).
- **Pre-warm first** so codex's lean-lsp probes don't cold-start, e.g.
  `lake -d CausalSmith build <the target modules>`.
- It does NOT exercise the boundary cap/escalation logic or the deterministic floors
  (freeze / fold / snapshot) — only the reviewer + prompt + skeleton. Those paths are
  covered by `test/formalization/`.

## Other relocated dev / one-off scripts

- `regen_snippets.ts` — one-off: re-extract `statement` fields in a bundle's
  `lean_snippets.json` with the current `lean_extract` (fixes snippets captured by an
  older extractor). `npx tsx scripts/dev/regen_snippets.ts <bundleDir>`.
- `migrate_bank_stage_prose.mjs` (+ `.d.mts`) — one-off bank migration (old bare-number
  stage ids → `D-`/`F-` labels in bank README prose). Tested by
  `test/migrate_bank_stage_prose.test.ts`. `node scripts/dev/migrate_bank_stage_prose.mjs`.
- `watch.py` — ad-hoc poller that tails active research runs (hardcoded run list / path;
  edit before use). Pure scratch monitoring helper.
