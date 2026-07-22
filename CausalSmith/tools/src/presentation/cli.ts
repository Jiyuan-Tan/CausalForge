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
    "usage: causalsmith present <qid> <spec> [--resume] [--auto] [--dry-run] [--revise] [--stop-after P0..P5] [--from P0..P5] [--max-p5-reviews N]",
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
  let maxP5Reviews: number | undefined;
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--resume") resume = true;
    else if (a === "--auto") auto = true;
    else if (a === "--dry-run") dryRun = true;
    else if (a === "--revise") revise = true;
    else if (a === "--stop-after") stopAfter = argv[++i];
    else if (a === "--from") from = argv[++i];
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
    // Presentation work uses the dedicated 5.5 tier for literature breadth and
    // journal-style prose. Individual stages still own their task-specific effort.
    // Env: CAUSALEAN_MODEL_CODEX_PRESENT.
    runCodex: (args) => runCodex({ cwd: args.cwd, prompt: args.prompt, reasoningEffort: args.reasoningEffort, leanLsp: args.leanLsp, model: args.model ?? MODELS.codexPresentation }),
    dryRun,
  };
  // Per-run agent-call transcript (every codex/claude INPUT + OUTPUT), mirroring
  // causalsmith's `_agent_logs`. Created once at run start so the folder exists before
  // any stage dispatches; calls append across --resume / --from re-entries.
  const runLogsDir = ensureLogsDir(repoRoot, qid, spec);
  const logFile = join(runLogsDir, "agent_calls.log");
  const deps = withAgentLogging(baseDeps, logFile);

  // P0--P5 mutate one shared bundle.  A foreground terminal may report its
  // child complete before the child exits, so refuse a second invocation until
  // the first has released its durable heartbeat.
  const { halt } = await withRunHeartbeatAt(runLogsDir, qid, spec, () =>
    runPaperPipeline({ repoRoot, qid, spec, deps, resume, auto, stopAfter: parsedStop, from: parsedFrom, maxP5Reviews }),
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
