#!/usr/bin/env node
/**
 * causalsmith <qid> <spec> [--resume] [--auto] [--dry-run] [--stop-after P0..P5] [--from P0..P5] [--max-p5-reviews N]
 *
 * Presentation pipeline: accepted bank entry → arXiv-grade paper bundle → P5
 * referee review. Normally halts at two user checkpoints (after P1: outline + bibliography;
 * after P2: first full draft); --auto approves both while preserving hard halts. The
 * final stage P5 sends the paper to a codex referee and writes p5_review.{json,md}.
 * Safe prose/structure findings go to one holistic reviser for at most two passes;
 * source-truth/citation findings halt with p5_revision_routing.md.
 */
import { readFile } from "node:fs/promises";
import { join } from "node:path";
import { runPaperPipeline, type PaperDeps } from "./pipeline.js";
import { PaperStage } from "./types.js";
import { presentationDir, ensureLogsDir } from "./paths.js";
import { findCausalSmithRoot } from "../shared/repo_root.js";
import { withAgentLogging } from "./agent_log.js";
import { runCodex } from "../shared/codex.js";
import { withRunHeartbeatAt } from "../shared/run_heartbeat.js";
import { runClaude } from "../workers/claude.js";
import { MODELS } from "../models.js";

function usage(): never {
  console.error(
    "usage: causalsmith present <qid> <spec> [--resume] [--auto] [--dry-run] [--revise] [--reassemble] [--refresh-frozen-bodies] [--promote-again] [--reuse-existing-proofs-for-audit] [--refresh-statement-audit] [--stop-after P0..P5] [--from P0..P6] [--max-p5-reviews N] [--slides] [--refresh-slides]",
  );
  process.exit(2);
}

/** Run the presentation pipeline behind `causalsmith present`. */
export async function runPresentationCli(argv: string[]): Promise<void> {
  const positional: string[] = [];
  let resume = false;
  let auto = false;
  let dryRun = false;
  let stopAfter: string | undefined;
  let from: string | undefined;
  let revise = false;
  let reassembleP2 = false;
  let refreshFrozenBodies = false;
  let promoteAgain = false;
  let refreshStatementAudit = false;
  let reuseExistingProofsForAudit = false;
  let maxP5Reviews: number | undefined;
  let slides = false;
  let refreshSlides = false;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--resume") resume = true;
    else if (a === "--slides") slides = true;
    else if (a === "--refresh-slides") refreshSlides = true;
    else if (a === "--auto") auto = true;
    else if (a === "--dry-run") dryRun = true;
    else if (a === "--revise") revise = true;
    else if (a === "--reassemble") reassembleP2 = true;
    else if (a === "--refresh-frozen-bodies") refreshFrozenBodies = true;
    else if (a === "--promote-again") promoteAgain = true;
    else if (a === "--refresh-statement-audit") refreshStatementAudit = true;
    else if (a === "--reuse-existing-proofs-for-audit") reuseExistingProofsForAudit = true;
    else if (a === "--stop-after") {
      const value = argv[++i];
      if (!value || value.startsWith("--")) usage();
      stopAfter = value;
    }
    else if (a === "--from") {
      const value = argv[++i];
      if (!value || value.startsWith("--")) usage();
      from = value;
    }
    else if (a === "--max-p5-reviews") {
      const raw = argv[++i];
      maxP5Reviews = Number(raw);
      if (!Number.isInteger(maxP5Reviews) || maxP5Reviews < 1) usage();
    }
    else if (a.startsWith("--")) usage();
    else positional.push(a);
  }
  if (positional.length !== 2) usage();
  const [qid, spec] = positional;
  const parsedStop = stopAfter === undefined ? undefined : PaperStage.parse(stopAfter);
  const parsedFrom = from === undefined ? undefined : PaperStage.parse(from);
  if (parsedStop === "P6") {
    console.error("P6 (slides) is not part of the P0–P5 loop — run it with --slides (or --from P6) after P5 settles");
    process.exit(2);
  }
  if (refreshFrozenBodies && parsedFrom !== "P1") {
    console.error("--refresh-frozen-bodies requires --from P1 (it releases the audit-frozen bodies before the layer is re-planned)");
    process.exit(2);
  }
  if (reassembleP2 && parsedFrom !== "P2") {
    console.error("--reassemble requires --from P2 (it re-enters at assembly over the existing authored sources)");
    process.exit(2);
  }
  const repoRoot = findCausalSmithRoot(process.cwd());

  // `--revise`: read the existing P5 review and print the orchestrator routing plan
  // (kind→action). Read-only — no model calls, no stage execution.
  if (revise) {
    const { loadPriorReview } = await import("./revision_brief.js");
    const { renderRoutingPlan } = await import("./revision_routing.js");
    const outDir = presentationDir(repoRoot, qid, spec);
    const review = await loadPriorReview(outDir);
    if (!review) {
      console.error(`no p5_review.json in ${outDir} — run P5 first`);
      process.exit(1);
    }
    process.stdout.write(renderRoutingPlan(review));
    return;
  }

  const baseDeps: PaperDeps = {
    codexModel: MODELS.codexPresentation,
    runClaude: (args) => runClaude(args),
    // Presentation authoring uses the dedicated 5.5 tier for literature breadth and
    // journal-style prose. Individual stages may override it (P5 review uses Sol).
    // Env: CAUSALEAN_MODEL_CODEX_PRESENT.
    runCodex: (args) => runCodex({ cwd: args.cwd, prompt: args.prompt, reasoningEffort: args.reasoningEffort, leanLsp: args.leanLsp, webSearch: args.webSearch, model: args.model ?? MODELS.codexPresentation }),
    dryRun,
  };
  // Per-run agent-call transcript (every codex/claude INPUT + OUTPUT), mirroring
  // causalsmith's `_agent_logs`. Created once at run start so the folder exists before
  // any stage dispatches; calls append across --resume / --from re-entries.
  const runLogsDir = ensureLogsDir(repoRoot, qid, spec);
  const logFile = join(runLogsDir, "agent_calls.log");
  const deps = withAgentLogging(baseDeps, logFile);

  // P6 — slides. Deliberately OUTSIDE runPaperPipeline: it is terminal and optional,
  // runs only once the paper is settled (P5 completed, nothing pending), and must
  // never join the P0–P5 revision loop's cache fan-out. One codex call; slides.md is
  // an authored source whose hand edits survive re-runs (see stages/p6_slides.ts).
  if (slides || refreshSlides || parsedFrom === "P6") {
    if (resume || auto || revise || reassembleP2 || refreshFrozenBodies || promoteAgain ||
        refreshStatementAudit || reuseExistingProofsForAudit || stopAfter || maxP5Reviews ||
        (from !== undefined && parsedFrom !== "P6")) usage();
    const { loadBankEntry } = await import("./bank.js");
    const { loadPaperState, savePaperState } = await import("./state.js");
    const { stageP6 } = await import("./stages/p6_slides.js");
    const outDir = presentationDir(repoRoot, qid, spec);
    await withRunHeartbeatAt(runLogsDir, qid, spec, async () => {
      const state = await loadPaperState(outDir, qid, spec);
      if (!state) throw new Error("P6 requires an existing presentation run — run the paper pipeline first");
      // "P5 settled" = the referee has reviewed the CURRENT emitted paper and nothing is
      // mid-flight. A post-P5 `--from P4` re-emit legitimately leaves stage_completed=P4,
      // so the review file (P5 archives every pass) plus a P4/P5 boundary is the check —
      // not stage_completed === "P5" alone.
      const reviewed = await readFile(join(outDir, "p5_review.json"), "utf8").then(() => true, () => false);
      if (!reviewed || state.checkpoint_pending || !(state.stage_completed === "P4" || state.stage_completed === "P5")) {
        throw new Error(
          `P6 runs only after P5 is settled (stage_completed=${state.stage_completed}, ` +
            `checkpoint_pending=${state.checkpoint_pending ?? "none"}, p5_review.json ${reviewed ? "present" : "absent"}) — finish the paper first`,
        );
      }
      const bank = await loadBankEntry(repoRoot, qid, spec);
      await stageP6({
        ctx: { repoRoot, qid, spec, deps, outDir, refreshSlides },
        state,
        bank,
        outDir,
      });
      await savePaperState(outDir, state);
      const note = state.notes.filter((n) => n.startsWith("P6:")).at(-1);
      console.log(`${note ?? "P6: done"}\nCHECKPOINT (slides): read ${outDir}/slides.md for CLARITY — hand-edit it directly; edits are preserved.`);
    });
    return;
  }

  if (refreshStatementAudit) {
    if (reuseExistingProofsForAudit || resume || auto || dryRun || revise || stopAfter || from || maxP5Reviews) usage();
    const { loadBankEntry } = await import("./bank.js");
    const { loadPaperState, savePaperState } = await import("./state.js");
    const { runStatementAudit } = await import("./audit.js");
    const outDir = presentationDir(repoRoot, qid, spec);
    const problems = await withRunHeartbeatAt(runLogsDir, qid, spec, async () => {
      const state = await loadPaperState(outDir, qid, spec);
      if (!state) throw new Error("statement-audit refresh requires an existing presentation run");
      // A refresh may follow an edit made before this process started, so no
      // before/after comparison can certify the assembled manuscript current.
      // Persist the safe boundary first: even if auditing throws after a write,
      // resume must pass through cached P2 assembly before P4 can emit.
      state.stage_completed = "P1";
      state.checkpoint_pending = null;
      state.notes.push("Statement-audit refresh requires cached P2 reassembly before P4.");
      await savePaperState(outDir, state);
      const found = await runStatementAudit({
        ctx: { repoRoot, qid, spec, deps, outDir },
        state,
        bank: await loadBankEntry(repoRoot, qid, spec),
        outDir,
      });
      state.hard_gate_failures = found;
      if (found.length > 0) state.notes.push("Statement-audit refresh found unresolved drift; P4 remains blocked.");
      await savePaperState(outDir, state);
      return found;
    });
    console.log(`Statement audit refreshed: ${problems.length} problem(s); unchanged faithful entries were cached.`);
    if (problems.length > 0) process.exitCode = 1;
    return;
  }

  // P0--P5 mutate one shared bundle.  A foreground terminal may report its
  // child complete before the child exits, so refuse a second invocation until
  // the first has released its durable heartbeat.
  const { halt } = await withRunHeartbeatAt(runLogsDir, qid, spec, () =>
    runPaperPipeline({ repoRoot, qid, spec, deps, resume, auto, stopAfter: parsedStop, from: parsedFrom,
      maxP5Reviews, reuseExistingProofsForAudit, reassembleP2, refreshFrozenBodies, promoteAgain }),
  );
  const outDir = presentationDir(repoRoot, qid, spec);
  if (halt === "checkpoint:outline") {
    console.log(`CHECKPOINT (outline): review ${outDir}/outline.md, formal_layer.tex and references.bib, then rerun with --resume.`);
  } else if (halt === "checkpoint:draft") {
    console.log(`CHECKPOINT (draft): review ${outDir}/paper.tex, then rerun with --resume.`);
  } else if (halt === "done") {
    await surfaceReview(outDir);
  } else if (halt === "p5:adjudication") {
    console.log(`P5 REVISION HALT: source-truth, citation, or unclassified finding requires adjudication. See ${outDir}/p5_revision_routing.md.`);
  } else if (halt === "p5:iteration-cap") {
    console.log(`P5 REVISION HALT: two holistic revision passes are exhausted. See ${outDir}/p5_review.md, p5_review_history/, and p5_revision_routing.md.`);
  } else if (halt === "p5:research-required") {
    console.log(`P5 REVISION HALT: a major residual requires new research or source work, not another manuscript pass. See ${outDir}/p5_revision_routing.md.`);
  } else if (halt === "p5:stalled") {
    console.log(`P5 REVISION HALT: the holistic reviser produced no authored-source change. See ${outDir}/p5_review.md and p5_revision_routing.md.`);
  } else if (halt === "p5:review-cap") {
    console.log(`P5 REVIEW CAP: stopped after ${maxP5Reviews} referee pass(es). See ${outDir}/p5_review.md.`);
  } else {
    console.log(`CausalSmith present halt: ${halt} (artifacts in ${outDir})`);
  }
}

/** Print the P5 referee verdict so the orchestrator acts on it. */
async function surfaceReview(outDir: string): Promise<void> {
  const raw = await readFile(join(outDir, "p5_review.json"), "utf8").catch(() => null);
  if (raw === null) {
    console.log(`CausalSmith present halt: done (artifacts in ${outDir})`);
    return;
  }
  const r = JSON.parse(raw) as { recommendation: string; findings?: { severity: string }[] };
  const findings = r.findings ?? [];
  const majors = findings.filter((f) => f.severity === "major").length;
  if (r.recommendation === "accept" && findings.length === 0) {
    console.log(`P5 REVIEW: accept, no findings. Paper bundle ready in ${outDir}.`);
    return;
  }
  console.log(
    `P5 REVIEW: ${r.recommendation} — ${findings.length} findings (${majors} major). See ${outDir}/p5_review.md.\n` +
      `Holistic automatic revisions are exhausted; use p5_revision_routing.md to adjudicate the residual findings.`,
  );
}
