---
name: causalsmith-present
description: Internal presentation-mode workflow for `/causalsmith present` with a qid and specialization. Use when the CausalSmith skill enters presentation mode for an accepted bank entry, producing an arXiv-grade paper bundle and interactive web artifacts. The pipeline owns P0–P5; the orchestrator reviews checkpoints and manually adjudicates any frozen-layer versus Lean disagreement.
---

# /causalsmith present — entry point

Input: an **accepted** bank entry (`CausalSmith/doc/research/_bank/accepted/<qid>_<spec>/`). Output: a working-paper bundle in `CausalSmith/doc/presentation/<qid>_<spec>/` (paper.tex/pdf, presentation_crosswalk.json, lean_snippets.json, paper_body.html, assumption_table.md, meta.json) that `CausalSmith/site/` renders as an interactive verified paper.

## Mechanics

1. Launch from `CausalSmith/tools/` (cwd matters):
   `npx tsx bin/causalsmith.ts present <qid> <spec> [--resume] [--dry-run] [--stop-after P0..P5] [--from P0..P5]`
   Long stages go in background; pre-warm the Lean build (`lake -d CausalSmith build <research modules>`; fetch the Mathlib cache first if oleans are missing) before P2/P3 so codex's lean-lsp calls don't cold-start.
2. The pipeline halts at two checkpoints — after P1 (outline + frozen layer + bibliography) and after P2 (full draft). Review the named artifacts, then `--resume`. The P1 review MUST include a notation-resolvability scan: every operator/predicate symbol used across the frozen envs (grep for `\mathrm{`-style names) has exactly one defining statement ("We say ... holds when") and every later use anchors back to it via `\ref{obj:...}` — an unresolvable symbol is a self-containedness defect to fix before approving (PolyTail incident, 2026-06-11). With user authorization you may approve checkpoints yourself; record what you checked.
3. State machine: `<qid>_<spec>_paper_state.json` (`stage_completed`, `checkpoint_pending`, `revision_round`, `notes`). To re-run a stage, rewind `stage_completed` to the previous stage (and clear `checkpoint_pending`/`revision_round`) and `--resume`. Delete stale stage outputs only when you intend regeneration — see caches below.
4. P5 (terminal) sends the FINAL `paper.tex` to a codex referee (reviews it as a journal submission) and writes `p5_review.{json,md}` — the review is RETURNED, never auto-applied. On `halt: done`, read `p5_review.md`: address every finding in `paper.tex` yourself (this is the orchestrator's job, like equivalence adjudication — the pipeline does not edit the paper for you), then re-run `--from P4` to re-emit the bundle and re-review. A claim-fidelity finding that traces to the frozen layer / Lean (not just prose) is an adjudication item, not a prose patch.
5. When the run completes and the review is clean (or its findings are addressed), strip latexmk aux files and commit the bundle dir; verify with a site build (`cd CausalSmith/site && npx astro build` — its loadBundle integrity gate must pass).

## Stages and where to look

| Stage | Output to inspect | Failure modes seen live |
|---|---|---|
| P0 literature | `references.bib`, `references_raw.bib`, `p0_verification.json`, `related_work_brief.md` | verification drops: check raw vs kept; a high drop rate is a lookup defect, not hallucination (stage throws >40%) |
| P1 plan | `outline.md`, `formal_layer.tex`, `frozen_hashes.json` | outline/env validation throws with explicit reasons; frozen bodies inherit note ambiguity — the P3 equivalence gate is what catches that |
| P2 draft | `sections/*.tex`, `proofs/<T-id>.tex`, `front_matter.tex`, `paper.tex` | lint throws on frozen-drift / objid-in-prose; fix the cached artifact, not paper.tex |
| P3 gates | `reviews.jsonl`, `equivalence_cache.json`, `gate_cache.json` | see "Equivalence adjudication" below; other gate failures revise automatically (max 3 rounds) |
| P4 emit | bundle files, `paper.pdf` | compile loop (codex fixes); `lean_snippets.json` badges; entry lint |
| P5 review | `p5_review.json`, `p5_review.md` | codex referee on final paper; returns recommendation + findings — orchestrator fixes `paper.tex`, then `--from P4` to re-emit + re-review |

## Cost economy (user directive — P3 is the bottleneck)

P3 ≈ 30 codex equivalence audits (tiered effort: T-/L- statements high, P-* definitions/assumptions medium) + codex-high proof audits + ~60–80 citation checks (low) + opus overclaim + opus×1+codex×1 rubric. **Never rerun without a material change; mine every run fully.**
- All gate verdicts are content-keyed cached: `equivalence_cache.json` (env body + crosswalk mapping), `gate_cache.json` (proof audit, citation support, overclaim, rubric). Reruns only re-pay for changed inputs; delete a cache file to force a fresh audit.
- P2 artifacts are file-cached (sections/, proofs/, front_matter.tex): a P2 retry reuses them; delete a file to regenerate it. After amending the frozen layer, sync the env copies inside cached sections and re-pin `frozen_hashes.json` (bodies are hashed; titles are not).
- When an adjudication preserves content, seed the caches rather than re-auditing (compute keys with `hashEnvBody(body + "|" + file:decl:line)`).
- `citation-unverifiable` is an advisory (logged, never failed, never revised) — only `unsupported` (contradiction/overreach) blocks.
- P4 re-verifies cited entries against Crossref/arXiv. The fetch throttle is per-process, so running several `--from P4` re-emits **concurrently** can rate-limit the registries. A transient "registry unreachable" on an entry that carries a DOI/arXiv id is now kept as a non-blocking caveat (a `P4: … kept with caveat` note), not a hard fail — a fabricated/absent id (reachable 4xx / empty feed) still hard-fails. For a clean full re-emit, prefer running P4 sequentially (or a few at a time).

## Equivalence adjudication — the orchestrator's MANUAL job

The P3 equivalence gate compares each frozen statement against its crosswalk-named Lean decl (codex + lean-lsp, equivalence rule: conclusions must match, the paper may not omit a load-bearing Lean hypothesis, and it may not carry a load-bearing hypothesis/restriction the Lean does not require anywhere — equivalent up to packaging and incidental implicit regularity). It runs ONCE, before the revise loop, because revision can never fix it. **On failure the pipeline sweeps the remaining gates (cache-filling), then HALTS. It does not repair anything itself — by design.** The crosswalk is the trust anchor; an automated "repair" that re-points the paper at a wrong decl would make the gate pass against the wrong target, silently. Wrong mappings must fail loudly; only the orchestrator mutates them.

For each flagged statement, diagnose which of three cases it is:

1. **Wrong crosswalk mapping** (symptom: "the decl only proves <something generic/unrelated>"). Find the real decl — grep the research Lean files for name-affine lemmas (`l14_*` for L-14; they are often `private lemma`s inside the T-blocks). Read the statement to confirm, then patch the bank's `*_crosswalk_full.json` (keep a `.bak`).
2. **Note overstates Lean** (symptom: the paper claims component facts / exact identities / dependency sets the decl doesn't expose). Read the actual Lean conclusion, then amend the frozen body to the Lean-true form: re-pin hashes, sync cached sections, reseed the equivalence cache for unchanged entries. Do NOT edit the accepted note — flag the discrepancy for a future note revision.
3. **Auditor miscalibration** (packaging differences reported as drift). Fix the gate prompt with a general rule, never an instance hack.

Every adjudication gets a record: `_causalsmith_present_adjudication_<date>.md` in the bank entry dir (what was flagged, the verdict per statement, what was edited where, backups), plus a line in the paper state `notes`. Commit the bank edit separately from pipeline-code commits.

After adjudication also sweep the **prose** of sections containing amended envs — section text written against the old statement can contradict the new one, and no gate checks body-prose-vs-definition consistency.

## Self-improving loop

Same contract as /causalsmith research: the pipeline is the tool; when a stage misbehaves, prefer fixing the tool (prompt/code, as a general rule) over hand-patching the instance, verify with the test suite (`npx vitest run test/presentation_ --no-isolate --no-file-parallelism --maxWorkers=1` + `npx tsc --noEmit`), commit each fix separately, and only then rerun the stage. Tests must never touch live run dirs (pass `outDir` overrides). Record recurring lessons in prompts only on the second occurrence of a failure class.

Known sharp edges: run all commands with explicit cwd (background shells reset it); CausalSmith present deliberately does not import `src/cli.ts` (the CausalSmith research graph) — keep it that way so in-flight CausalSmith research edits can't crash a paper run.
