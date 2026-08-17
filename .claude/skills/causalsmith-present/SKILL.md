---
name: causalsmith-present
description: Internal presentation-mode workflow for `/causalsmith present` with a qid and specialization. Use when the CausalSmith skill enters presentation mode for an accepted bank entry, producing an arXiv-grade paper bundle and interactive web artifacts. The pipeline owns P0–P5; the orchestrator reviews checkpoints and manually adjudicates any frozen-layer versus Lean disagreement.
---

# /causalsmith present — entry point

Input: an **accepted** bank entry (`CausalSmith/doc/research/_bank/accepted/<qid>_<spec>/`). Output: a working-paper bundle in `CausalSmith/doc/presentation/<qid>_<spec>/` (paper.tex/pdf, presentation_crosswalk.json, lean_snippets.json, paper_body.html, assumption_table.md, meta.json) that `CausalSmith/site/` renders as an interactive verified paper.

**Authorship standard:** write a natural, conventional paper for the field, not a prose translation of Lean. The main text must lead with the scientific question, ordinary mathematical formulation, intuition, results, and relation to the literature. Treat Lean as the verification backend: keep declaration names, proof-engineering structure, certified-representation records, execution traces, and other formalization machinery out of the main exposition unless they are themselves scientifically essential; place necessary implementation detail in a clearly motivated technical appendix or the interactive verification layer.

## Mechanics

1. Launch from `CausalSmith/tools/` (cwd matters):
   `npx tsx bin/causalsmith.ts present <qid> <spec> [--resume] [--dry-run] [--stop-after P0..P5] [--from P0..P5]`
   Long stages go in background; pre-warm the Lean build (`lake -d CausalSmith build <research modules>`; fetch the Mathlib cache first if oleans are missing) before P2/P3 so codex's lean-lsp calls don't cold-start.
2. The pipeline halts at two checkpoints — after P1 (outline + frozen layer + bibliography) and after P2 (full draft). Review the named artifacts, then `--resume`. At the P1 checkpoint read `notation_review.json`: the codex notation reviewer is the ONE semantic notation authority, and its residue arrives as `advisories` (`notation-unresolved` = the one allowed synthesis attempt for a symbol failed or was re-flagged; the symbol still lacks a reader-facing definition). Resolve each advisory yourself — edit the note/outline/graph statement or accept it with a recorded reason — before approving; an unresolvable symbol is a self-containedness defect (PolyTail incident, 2026-06-11). With user authorization you may approve checkpoints yourself; record what you checked.
3. State machine: `<qid>_<spec>_paper_state.json` (`stage_completed`, `checkpoint_pending`, `revision_round`, `notes`). Use `--from P0..P5` to re-enter the stage that actually owes work; do not hand-edit the pointer merely to retry a stage. A semantic rewind to an earlier stage is reserved for an authorship, mathematical, frozen-layer, or substantive presentation-plan change. Delete stale stage outputs only when you intend semantic regeneration — see caches below.
4. P5 (terminal) sends the FINAL `paper.tex` to a codex referee (reviews it as a journal submission) and writes `p5_review.{json,md}` — the review is RETURNED, never auto-applied. On `halt: done`, read `p5_review.md`: address every finding in `paper.tex` yourself (this is the orchestrator's job, like equivalence adjudication — the pipeline does not edit the paper for you), then re-run `--from P4` to re-emit the bundle and re-review. Stop early when clean or all findings are addressed; never exceed four P5 revision passes total, counting the two automatic revisions. At the cap, record any unresolved findings without another revision. A claim-fidelity finding that traces to the frozen layer / Lean (not just prose) is an adjudication item, not a prose patch.
5. When the run completes and the review is clean (or its findings are addressed), strip latexmk aux files and commit the bundle dir; verify with a site build (`cd CausalSmith/site && npx astro build` — its loadBundle integrity gate must pass).

## Repair and re-entry discipline

- Rewind only for a real math, authorship, frozen-content, outline, or exposition-plan change.
- For mechanical failures, inspect emitted versus persisted I/O, repair/replay in place, and re-run the stage —
  P1 recovery is CACHE-based: renders, notation reviews, and accepted synthesized definitions all live in
  `p1_cache.json`, so a re-run mostly re-pays only for changed inputs (defect-driven re-renders are deliberately
  uncached, so envs the reviewer flagged for wording are re-authored each run). There is no adjudication
  side-channel: when P1 fails or leaves advisories, fix the blocking input (note/outline/graph) and re-run
  `--from P1`. Use `--from <stage>` only when semantic content changed, and invalidate only changed content.
- The synthesis LEDGER (`synth` in `p1_cache.json`, mirrored in `notation_review.json`) grants each notation
  symbol ONE synthesis attempt, ever. Accepted entries are the durable store of synthesized definitions across
  re-runs; failed/re-flagged entries surface as `notation-unresolved` advisories at the checkpoint. Delete a
  symbol's ledger entry (or the whole cache file) to let a re-run try synthesis again after you fixed its input.
- Cache keys embed per-purpose fingerprints of the P1 prompt files (outline / render / notation): editing a
  prompt auto-invalidates its consumer's cache — never bump a version string by hand. Exception: the synthesis
  ledger is one-attempt-ever and prompt-independent — editing `p1_synthesize_definition.txt` re-arms nothing;
  delete the affected ledger entries to retry.
- A legacy bundle whose proof cache predates the current key format simply re-renders its proofs on the
  next P2 run; to keep existing rendered proofs instead, re-enter with `--reuse-existing-proofs-for-audit`
  (each reused proof still gets a fresh mandatory audit).
- Never synthesize a presentation-only definition for Lean-backed notation (the router enforces this: a
  Lean-realized symbol's missing definition re-renders its designated home env, or halts if that home is locked
  or missing). Resolve or clarify its existing Lean/graph home; synthesis is allowed only when no corresponding
  Lean realization exists.

## Stages and where to look

| Stage | Output to inspect | Failure modes seen live |
|---|---|---|
| P0 literature | `references.bib`, `references_raw.bib`, `p0_verification.json`, `related_work_brief.md` | verification drops: check raw vs kept; a high drop rate is a lookup defect, not hallucination (stage throws >40%) |
| P1 plan | `outline.md`, `formal_layer.{json,tex}` (each block's `body` IS the freeze), `equivalence_cache.json` | outline/env validation throws with explicit reasons; the P1 STATEMENT equivalence audit (see "Equivalence adjudication" below) refines each frozen body toward Lean and halts on residual drift |
| P2 draft | `sections/*.tex`, `proofs/<T-id>.tex`, `front_matter.tex`, `paper.tex`, `proof_audit_cache.json` | lint throws on frozen-drift / objid-in-prose (fix the cached artifact, not paper.tex); the P2 PROOF equivalence audit refines prose proofs toward Lean and halts on residual unfaithfulness |
| P3 gates | `logs/reviews.jsonl`, `gate_cache.json` | prose-quality gates only (overclaim, citation support, rubric); failures revise automatically (max 2 rounds) |
| P4 emit | bundle files, `paper.pdf` | compile loop (codex fixes); `lean_snippets.json` badges; entry lint; undocumented Lean decls block the emit (docstrings are authored at F5 — add them to the sources, then `--from P4`) |
| P5 review | `p5_review.json`, `p5_review.md` | codex referee on final paper; returns recommendation + findings — orchestrator fixes `paper.tex`, then `--from P4` to re-emit + re-review |

## Cost economy (user directive — the audits are the bottleneck)

P1 ≈ 30 codex statement-equivalence audits (tiered effort: T-/L- statements high, P-* definitions/assumptions medium). P2 ≈ one codex-high proof audit per rendered proof. P3 ≈ ~60–80 citation checks (low) + opus overclaim + opus×1+codex×1 rubric. **Never rerun without a material change; mine every run fully.**
- All audit/gate verdicts are content-keyed cached: `equivalence_cache.json` (P1 statement audit), `proof_audit_cache.json` (P2 proof audit), `gate_cache.json` (P3 citation support, overclaim, rubric). Reruns only re-pay for changed inputs; delete a cache file to force a fresh audit.
- P2 artifacts are file-cached (sections/, proofs/, front_matter.tex): a P2 retry reuses them; delete a file to regenerate it. After amending the frozen layer, sync the env copies inside cached sections — each block's `body` in `formal_layer.json` is the freeze itself (whitespace-insensitive compare; titles are not frozen).
- Never hand-compute a cache key. To reseed after adjudicating an auditor FALSE POSITIVE: flip that obj_id's `verdict` to `"faithful"` in the cache file and leave its stored `key` untouched (the key was stamped by the audit run; it stays valid while the content is unchanged). Any content change invalidates the key automatically and the next run re-audits.
- `citation-unverifiable` is an advisory (logged, never failed, never revised) — only `unsupported` (contradiction/overreach) blocks.
- P4 re-verifies cited entries against Crossref/arXiv. The fetch throttle is per-process, so running several `--from P4` re-emits **concurrently** can rate-limit the registries. A transient "registry unreachable" on an entry that carries a DOI/arXiv id is now kept as a non-blocking caveat (a `P4: … kept with caveat` note), not a hard fail — a fabricated/absent id (reachable 4xx / empty feed) still hard-fails. For a clean full re-emit, prefer running P4 sequentially (or a few at a time).

## Equivalence adjudication — the orchestrator's MANUAL job

Equivalence is audited where the artifact is produced: the P1 STATEMENT audit compares each frozen env body against its crosswalk-named Lean decl the moment it is rendered (codex + lean-lsp, equivalence rule: conclusions must match, the paper may not omit a load-bearing Lean hypothesis, and it may not carry a load-bearing hypothesis/restriction the Lean does not require anywhere — equivalent up to packaging and incidental implicit regularity); the P2 PROOF audit does the same for each prose proof against its Lean proof. Both auto-refine drift TOWARD Lean (≤2 rounds — always safe, Lean type-checks) and persist the refined text; residual drift HALTS the stage for you. **The pipeline never repairs a mapping itself — by design.** The crosswalk is the trust anchor; an automated "repair" that re-points the paper at a wrong decl would make the audit pass against the wrong target, silently. Wrong mappings must fail loudly; only the orchestrator mutates them.

For each flagged statement, diagnose which of three cases it is:

1. **Wrong crosswalk mapping** (symptom: "the decl only proves <something generic/unrelated>"). Find the real decl — grep the research Lean files for name-affine lemmas (`l14_*` for L-14; they are often `private lemma`s inside the T-blocks). Read the statement to confirm, then patch the bank's `*_crosswalk_full.json` (keep a `.bak`).
2. **Note overstates Lean** (symptom: the paper claims component facts / exact identities / dependency sets the decl doesn't expose). Read the actual Lean conclusion, then amend the frozen body to the Lean-true form: sync cached sections, and re-run `--from P1` so the changed body is re-audited (unchanged entries hit their cache). Do NOT edit the accepted note — flag the discrepancy for a future note revision.
3. **Auditor miscalibration** (packaging differences reported as drift). Fix the gate prompt with a general rule, never an instance hack.

Every adjudication gets a record: `_causalsmith_present_adjudication_<date>.md` in the bank entry dir (what was flagged, the verdict per statement, what was edited where, backups), plus a line in the paper state `notes`. Commit the bank edit separately from pipeline-code commits.

After adjudication also sweep the **prose** of sections containing amended envs — section text written against the old statement can contradict the new one, and no gate checks body-prose-vs-definition consistency.

## Self-improving loop

Same contract as /causalsmith research: the pipeline is the tool; when a stage misbehaves, prefer fixing the tool (prompt/code, as a general rule) over hand-patching the instance, verify with the test suite (`npx vitest run test/presentation_` + `npx tsc --noEmit`), commit each fix separately, and only then rerun the stage. Tests must never touch live run dirs (pass `outDir` overrides). Record recurring lessons in prompts only on the second occurrence of a failure class.

Every presentation-pipeline change, including every prompt change, requires a PASS from an independent agent audit before it is committed or used by a live run. The auditor must inspect the exact diff for necessity, generality, minimal wording, and adequate targeted verification; the change's author may not self-certify it. Remove instance-specific or redundant prompt text before approval, and record the audit result.

Known sharp edges: run all commands with explicit cwd (background shells reset it); CausalSmith present deliberately does not import `src/cli.ts` (the CausalSmith research graph) — keep it that way so in-flight CausalSmith research edits can't crash a paper run.
