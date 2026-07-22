// Formalization Stage 5. Extracted from pipeline_stages.ts in Step 2.3 of the three-submodules refactor.

import path from "node:path";
import { readFile } from "node:fs/promises";
import { MODEL_PLAN } from "../constants.js";
import type { AddedAssumption, PipelineContext, StageResult, StateJson } from "../types.js";
import {
  artifactPaths,
  baseBrief,
  parseStageOutput,
  readPrompt,
  type StageDeps,
} from "../pipeline_support.js";
import { buildCompleteCrosswalk, buildCompleteCrosswalkFromGraph, parseLeanDecls, persistCrosswalk, crosswalkVerifiedWithoutAnchor } from "./crosswalk.js";
import { graphPath, loadGraph } from "../graph/store.js";
import { existsSync } from "node:fs";
import { bankSoundnessIssues } from "./bank_soundness.js";
import { CoreSchema } from "../discovery/core/schema.js";
import { coreJsonPath } from "../discovery/stages/d0_core.js";
import { PlanSchema } from "./plan/schema.js";
import { auditCitedReview, auditDelivery } from "./delivery_audit.js";
import { dispatchAgent } from "../framework/agent_dispatch.js";

/**
 * Emit the COMPLETE tex↔Lean crosswalk (the visualization backbone AND the table
 * causalsmith consumes). F5 is the guaranteed-final point: F4 has passed, no stage
 * edits Lean past here, so the lemma set is final and line numbers are accurate.
 * Lemma-inclusive; inherits the F2.5 drift verdicts for the def/theorem rows.
 *
 * NO LONGER best-effort. A silently-swallowed emit failure left the PREVIOUS
 * (pre-de-laundering) table banked as if current — the bug behind P-8 shipping
 * `lean: null` with a stale `equivalent` verdict. On emit failure, or a
 * self-consistency contradiction (a row claiming a verified match with no anchor),
 * return a block reason so F5 refuses to reach CKPT 2 with a stale/inconsistent
 * table. Returns `null` on success.
 */
async function emitCompleteCrosswalk(args: {
  ctx: PipelineContext;
  state: StateJson;
}): Promise<string | null> {
  const paths = artifactPaths(args.ctx, args.state);
  let full;
  try {
    // Prefer the core-keyed graph (the trust anchor — carries every paper object,
    // its Lean link, and its obj_id alias). Fall back to the legacy .md parse only
    // when no graph exists (a pre-migration run).
    const gp = graphPath(paths.formalizationDir, args.ctx.qid, args.ctx.specialization);
    full = existsSync(gp)
      ? await buildCompleteCrosswalkFromGraph(await loadGraph(gp), paths.leanDir)
      : await buildCompleteCrosswalk(paths.leanDir, paths.md, args.state.flags.f25_crosswalk);
    await persistCrosswalk(paths.crosswalkFullJson, paths.crosswalkFullMd, full);
  } catch (err) {
    return (
      `F5 crosswalk emit FAILED (${err instanceof Error ? err.message : String(err)}) — ` +
      `the banked table would be STALE (the previous, pre-restructure table stays in place). ` +
      `Resolve the emit error then resume; do NOT bank.`
    );
  }
  console.warn(
    `[causalsmith] F5 complete crosswalk: ${full.length} object(s) anchored → ${paths.crosswalkFullJson}`,
  );
  const contradictions = crosswalkVerifiedWithoutAnchor(full);
  if (contradictions.length > 0) {
    return (
      `F5 crosswalk consistency: ${contradictions.length} row(s) claim a verified Lean match ` +
      `(exact/equivalent) but carry NO anchor — equivalence verified against nothing, and a ` +
      `consumer's gate SKIPS lean:null rows: ${contradictions.map((c) => `${c.obj_id} [${c.verdict}]`).join(", ")}. ` +
      `Wire the anchor (its decl exists) or correct the verdict to 'unmatched' before banking.`
    );
  }
  return null;
}

/**
 * #5 fix (F3→note→paper faithfulness). A premise F3 added to a theorem signature
 * (`state.added_assumptions`) that is LOAD-BEARING (not `regularity-bookkeeping`)
 * must be reflected in the .md note's hypothesis ledger — that note is what
 * causalsmith consumes, and causalsmith's assumption-table totality gate only sees
 * `(H<n>` binders, so an instance-implicit / differently-named F3 premise can be
 * silently omitted from the paper (overclaim-by-omission). A prose note may label
 * the same premise differently, so a deterministic label match would false-block a
 * correctly hand-synced note; this is therefore a PROMPTED CKPT-2 warning (it lists
 * exactly which premises to confirm), recorded durably in `design_decisions`.
 */
/**
 * Whether `label` occurs in the note as a STANDALONE token.
 *
 * A bare `includes` is satisfied by any longer label that contains it — `A1` by an unrelated
 * `A10` row — which suppresses the warning in exactly the case it exists to catch. Delimiters
 * are "not alphanumeric", so ordinary note punctuation (`**A1**:`, `(A1)`, `` `A1` ``) still
 * counts as a mention while `A10` does not.
 */
function noteMentionsLabel(noteMd: string, label: string): boolean {
  const l = label.trim();
  if (!l) return false;
  const esc = l.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return new RegExp(`(?:^|[^A-Za-z0-9])${esc}(?:$|[^A-Za-z0-9])`).test(noteMd);
}

export function unsyncedLoadBearingAssumptions(state: StateJson, noteMd: string): AddedAssumption[] {
  return state.added_assumptions.filter(
    (a) => a.classification !== "regularity-bookkeeping" && !noteMentionsLabel(noteMd, a.label),
  );
}

export async function runStage5(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  // Re-run the same omission contract used by F2 and accepted banking. F4 receipts are
  // mandatory here; any later plan/graph edit invalidates their evidence hashes.
  {
    const paths = artifactPaths(args.ctx, args.state);
    try {
      const core = CoreSchema.parse(JSON.parse(await readFile(coreJsonPath(args.ctx), "utf8")));
      const plan = PlanSchema.parse(JSON.parse(await readFile(paths.plan, "utf8")));
      const gp = graphPath(paths.formalizationDir, args.ctx.qid, args.ctx.specialization);
      const graph = await loadGraph(gp);
      const declNames = (await parseLeanDecls(paths.leanDir, { includeLemmas: true })).map((decl) => decl.name);
      const findings = auditDelivery({
        core,
        plan,
        graph,
        leanDeclNames: declNames,
        receipts: args.state.delivery_review_receipts ?? [],
        requireReceipts: true,
      });
      findings.push(...auditCitedReview({
        plan,
        graph,
        receipts: args.state.cited_review_receipts ?? [],
      }));
      if (findings.length > 0) {
        return {
          stage: "5",
          status: "checkpoint",
          advance: false,
          message: `F5 delivery audit REFUSED: ${findings.map((f) => `${f.code}${f.node_id ? ` @ ${f.node_id}` : ""}: ${f.message}`).join("; ")}`,
          artifacts: [],
        };
      }
    } catch (err) {
      return {
        stage: "5",
        status: "checkpoint",
        advance: false,
        message: `F5 delivery audit could not validate the artifacts: ${err instanceof Error ? err.message : String(err)}`,
        artifacts: [],
      };
    }
  }
  // Bank-soundness gate: refuse to reach CKPT 2 while the artifact (or any
  // reachable CausalSmith/Mathlib file) still contains a real `sorry` or a
  // cheat token (`axiom`/`opaque`/`native_decide`/`unsafe`). Text-based scan;
  // catches the false-completion class where F3's in-subdir count was clean
  // but a dependency stub was not.
  {
    const paths = artifactPaths(args.ctx, args.state);
    const issues = await bankSoundnessIssues(paths.leanDir, args.ctx.repoRoot);
    if (issues.length > 0) {
      return {
        stage: "5",
        status: "checkpoint",
        advance: false,
        message:
          `F5 bank-soundness gate REFUSED: ${issues.slice(0, 10).join("; ")}` +
          (issues.length > 10 ? ` (+${issues.length - 10} more)` : "") +
          ". Resolve (prove the stubs / remove the cheat tokens) then resume; do NOT bank.",
        artifacts: [],
      };
    }
  }
  // F3→note sync warning: surface any load-bearing F3-added premise whose label
  // is absent from the note, so the orchestrator confirms it is reflected before
  // the human banks (causalsmith's totality gate cannot catch a non-H<n> binder).
  const noteSyncWarnings: string[] = [];
  {
    const paths = artifactPaths(args.ctx, args.state);
    // Fail CLOSED. causalsmith consumes this note when banking, so an unreadable one is a
    // blocking defect — and degrading it to "" would ALSO make every load-bearing premise look
    // unsynced, or (with no premises) emit a clean run over a note that is not there at all.
    let noteMd: string;
    try {
      noteMd = await readFile(paths.md, "utf8");
    } catch (e) {
      return {
        stage: "5",
        status: "blocked",
        advance: false,
        message:
          `F5 cannot read the formalization note at ${paths.md} ` +
          `(${e instanceof Error ? e.message : String(e)}). causalsmith consumes this note when ` +
          `banking, and the F3→note premise-sync check cannot run without it.`,
        artifacts: [],
      };
    }
    for (const a of unsyncedLoadBearingAssumptions(args.state, noteMd)) {
      const w =
        `F3-added load-bearing premise '${a.label}' (${a.classification ?? "?"}, source ${a.source ?? "?"}) ` +
        `is not found by label in the note — CONFIRM it is reflected in the note's "Load-bearing hypotheses" ` +
        `before banking (causalsmith consumes the note; its totality gate is blind to non-H<n>/instance binders).`;
      noteSyncWarnings.push(w);
      args.state.design_decisions[`note_sync:${a.label}`] = w;
    }
  }

  const crosswalkBlock = await emitCompleteCrosswalk(args);
  if (crosswalkBlock) {
    return { stage: "5", status: "checkpoint", advance: false, message: crosswalkBlock, artifacts: [] };
  }
  const prompt = [
    await readPrompt(args.ctx, "stage5_apiMd.txt"),
    "",
    baseBrief(args.ctx, args.state),
    "",
    "Update doc/API.md only in the cluster's Theorems subsection (one of Panel/Theorems, ExactID/Theorems, PartialID/Theorems, Stat/Theorems — pick using the brief's Cluster line / Lean target subdirectory). Every row must include a description.",
    "Return JSON with artifacts.",
  ].join("\n");
  const out = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "5",
    label: "F5 API.md updater",
    prompt,
    promptSources: ["stage5_apiMd.txt", "baseBrief"],
    model: MODEL_PLAN.stage5.model,
    reasoningEffort: MODEL_PLAN.stage5.effort,
  });
  const parsed = parseStageOutput(out.stdout);
  if (parsed.status !== "completed") {
    // why: F5 must not report CHECKPOINT 2/API.md success unless the worker completed.
    return {
      stage: "5",
      status: "blocked",
      advance: false,
      message: parsed.message ?? "F5 did not complete",
      artifacts: parsed.artifacts ?? [],
    };
  }
  const baseMsg = parsed.message ?? "CHECKPOINT 2 reached; API.md updated";
  const message =
    noteSyncWarnings.length > 0
      ? `${baseMsg}\n\n⚠ NOTE-SYNC — verify before banking:\n- ${noteSyncWarnings.join("\n- ")}`
      : baseMsg;
  return {
    stage: "5",
    status: "checkpoint",
    message,
    artifacts: parsed.artifacts ?? [path.join(args.ctx.repoRoot, "doc", "API.md")],
  };
}
